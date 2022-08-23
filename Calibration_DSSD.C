/********************************************************************************************************************************************************************
 * 
 *                                                        Sirius DSSD calibration code
 * -----------------------------------------------------------------------------------------------------------------------------------------------------------------
 * This code is intended to make quick calibration of the DSSD
 * The progam reads a root file in which traces along with the boardIds and channel Ids are saved
 * The signal amplitudes are measured using Jordanov trapezoidal filter
 * To get the best resolution, it is better to have the optimozed k and m parameters (Use Sirius_offline_analysis_code to optimize these parameters)
 * The fitted histograms and graphs of FWHM vs Board Id/ stripnumber are saved under the name "Spectra_%a_r%b-Numexo2.root", where %a and %b correspond to the runnumber 
 * and sub runnumber respectively  
 * The calibration parameters are saved in a txt file having "boardId  channelId  gain  offset" format 
 * -------------------------------------------------------------------------------------------------------------------------------------------------------------------------
 * 
 * Author : Rikel CHAKMA
 * Date   : 16/06/2022
 * *************************************************************************************************************************************************************************/


#include "TFile.h"
#include "TTree.h"
#include "TH1.h"
#include "TH2.h"
#include "TF1.h"
#include "TGraph.h"
#include "TGraphErrors.h"
#include "TSpectrum.h"
#include "TMath.h"
#include "TRandom3.h"
#include "TCanvas.h"
#include <iostream>
#include <string>
#include <fstream>
#include <vector>

using namespace std;
//----------few definations------------------
#define NBOARDS 16
#define NCHANNELS 16
#define NSTRIPS NBOARDS * NCHANNELS
#define TRACE_SIZE 990
#define sampling_period 5 //ns
#define timestamp_unit 10 //ns
#define Resistance 700. //All the ASIC resistors are 700 k Ohms
//-----------------------
//   DSSD  NUMEXO Boards
//-----------------------
#define MB1_P4_BOARD1 180
#define MB1_P4_BOARD2 181
#define MB1_P5_BOARD1 169
#define MB1_P5_BOARD2 165

#define MB2_P4_BOARD1 175
#define MB2_P4_BOARD2 173
#define MB2_P5_BOARD1 174
#define MB2_P5_BOARD2 171

#define MB3_P4_BOARD1 192
#define MB3_P4_BOARD2 164
#define MB3_P5_BOARD1 176
#define MB3_P5_BOARD2 178

#define MB4_P4_BOARD1 172
#define MB4_P4_BOARD2 177
#define MB4_P5_BOARD1 170
#define MB4_P5_BOARD2 179
//--------------------- progress bar--
#define ProgressBar "=========================================================================================================================="
#define ProgressBarWidth 50

inline static void printProgress (Long64_t i, Long64_t total )
{
  static Int_t percentage = 0;

  static Int_t noEntries_dividedby100 = total/100;
  //reset
  if( percentage > 100) {
    percentage = 0;
  }
  if(i == percentage * noEntries_dividedby100){
    Int_t value = percentage;
    Int_t left = percentage * ProgressBarWidth / 100;
    Int_t right = ProgressBarWidth - left;
    printf ("\rProgress |%.*s%*s| %3d%%", left, ProgressBar, right,  "",value);
    fflush (stdout);
    percentage++;
  }

}
//
 void PressEnterToContinue()
{
    Int_t c;
    printf( "Press ENTER to continue... and f to end the program!!! " );
    fflush( stdin );
    do
    {
	c = getchar(); 
        if(c == 'f') exit(-1);
    }
    while ((c != '\n') && (c != EOF));
}
//
class resolution_strip{
  public:
  resolution_strip(UShort_t b, UShort_t c, UShort_t k1, UShort_t m1, Double_t r){
    board = b;
    channel = c;
    k = k1;
    m = m1;
    FWHM = r;
  };
  UShort_t board;
  UShort_t channel;
  UShort_t k;
  UShort_t m;
  Double_t FWHM;
};
//----------comparator function------------------
bool compareFWHM(resolution_strip i,resolution_strip j) { return (i.FWHM < j.FWHM); }
//------------Crystalball function---------------
Double_t crystalball_function(Double_t x, Double_t alpha, Double_t n, Double_t sigma, Double_t mean) {
  // evaluate the crystal ball function
  if (sigma < 0.)     return 0.;
  Double_t z = (x - mean)/sigma; 
  if (alpha < 0) z = -z; 
  Double_t abs_alpha = std::abs(alpha);
  // double C = n/abs_alpha * 1./(n-1.) * std::exp(-alpha*alpha/2.);
  // double D = std::sqrt(M_PI/2.)*(1.+ROOT::Math::erf(abs_alpha/std::sqrt(2.)));
  // double N = 1./(sigma*(C+D));
  if (z  > - abs_alpha)
    return std::exp(- 0.5 * z * z);
  else {
    //double A = std::pow(n/abs_alpha,n) * std::exp(-0.5*abs_alpha*abs_alpha);
    Double_t nDivAlpha = n/abs_alpha;
    Double_t AA =  std::exp(-0.5*abs_alpha*abs_alpha);
    Double_t B = nDivAlpha -abs_alpha;
    Double_t arg = nDivAlpha/(B-z);
    return AA * std::pow(arg,n);
  }
}
//---------------overload the crystalball function--------
Double_t crystalball_function(const Double_t *x, const Double_t *p) {
  if ((!x) || (!p)) return 0.; 
  //par list: [Constant], [Alpha], [N], [Sigma], [Mean]
  return (p[0] * crystalball_function(x[0], p[3], p[4], p[2], p[1]));
}
//-----------define 2 peak fitting function-------------
Double_t fit_function(const Double_t *x, const Double_t *p) {

  return crystalball_function(&x[0], &p[0]) + crystalball_function(&x[0], &p[5]) ;
}

//TTree variables
static ULong64_t     timestamp;
static UInt_t        eventnumber;
static UShort_t      trace[TRACE_SIZE];
static UShort_t      Gain;
static UShort_t      board;
static UShort_t      channel;
static UShort_t      boardIdx;
//extracted data
static UShort_t      stripnumber;
static Double_t      Baseline;
static Double_t      signal_is;
static Double_t      Noise;//sigma
static Double_t      signalHeight;//max val - baseline
static UShort_t      RiseTime;
static UShort_t      Max_pos;
static UShort_t      Trigger;
static Double_t      filt_Amplitude;
//
UShort_t getboardIndex[200];
UShort_t fBoardList[NBOARDS]; 
//------------------Trapezoidal Filter variables---------
Double_t Capacitance;//in pF
Double_t RC_constant;
//arrays for trapezoidal filters
Double_t* array_u ; //!
Double_t* array_v ; //!
Double_t* array_d ; //!
Double_t* Rectangular; //!
Double_t* Trapezoidal; //!
//trapezoidal
UShort_t **k; //!
UShort_t **m; //!


//--------FPCSA gain in pF-----------
void set_DSSD_gain(Double_t gain)
{
    Capacitance = gain;
    RC_constant =  Resistance*Capacitance;
}
//----------get physical strip number of the DSSD---
UShort_t get_DSSD_strip_number(UShort_t *p_board, UShort_t *p_channel)
{
    UShort_t StripNo = 0;
    switch (*p_board) 
    {
	//-----------------MB1-------------
	case MB1_P4_BOARD1:
		StripNo = 63 - *p_channel;
		break;
	case MB1_P4_BOARD2:
		StripNo =  63 - *p_channel - NCHANNELS;
		break;
	case MB1_P5_BOARD1:
		StripNo = 63 - *p_channel - 2*NCHANNELS;
		break;
	case MB1_P5_BOARD2:
		StripNo = 63 - *p_channel - 3*NCHANNELS;
		break;
	//-----------------MB2-------------
	case MB2_P5_BOARD1:
		StripNo = 64 + *p_channel;
		break;
	case MB2_P5_BOARD2:
		StripNo = 64 + *p_channel + NCHANNELS;
		break;
	case MB2_P4_BOARD1:
		StripNo = 64 + *p_channel + 2* NCHANNELS;
		break;
	case MB2_P4_BOARD2:
		StripNo =  64 + *p_channel + 3*NCHANNELS;
		break;
	//-----------------MB3-------------
	case MB3_P4_BOARD1:
		StripNo = 128 + *p_channel;
		break;
	case MB3_P4_BOARD2:
		StripNo = 128 + *p_channel + NCHANNELS;
		break;
	case MB3_P5_BOARD1:
		StripNo = 128 + *p_channel + 2* NCHANNELS;
		break;
	case MB3_P5_BOARD2:
		StripNo = 128 + *p_channel + 3*NCHANNELS;
		break;
	//-----------------MB4-------------
	case MB4_P5_BOARD1:
		StripNo = 255 - *p_channel;
		break;
	case MB4_P5_BOARD2:
		StripNo = 255 - *p_channel - NCHANNELS;
		break;
	case MB4_P4_BOARD1:
		StripNo = 255 - *p_channel -2*NCHANNELS;
		break;
	case MB4_P4_BOARD2:
		StripNo = 255 - *p_channel -3*NCHANNELS;
		break;
	default:
		break;
    }

    return StripNo;
}
//------------------calculate signal's parameters from the trace-----------------
void GetSignalInfo()
{
    //search range
    Int_t n1 = 200;
    Int_t n2 = TRACE_SIZE -200;
    //Reset the values
    Baseline = 0;
    signal_is=0;
    Noise=0;//sigma
    signalHeight=0;//max val - baseline
    RiseTime=0;
    Max_pos=0;
    Trigger=0;
    //calculate baseline
    Double_t temp =0.;
    for (UShort_t i = n1; i < n1 + 51; i++) 
    {
	Baseline += (Double_t)trace[i];
    }
    Baseline /=  (Double_t)(50);
    //calculate the noise
    for (UShort_t i = n1; i < n1 + 51; i++) 
    {
	temp = ((Double_t)trace[i] - Baseline);
	Noise += temp*temp;
    }
    Noise = TMath::Sqrt(Noise/ (Double_t)(50));
    //determine the polarity of the signal
    for(UShort_t n = n1; n < n2; n++)
    {
	signal_is+=trace[n]- Baseline;
    }
    //Get max value and max pos
    UShort_t max_val = trace[10];
    UShort_t max_pos = 0;
    for (UShort_t i = n1; i < n2; i++) 
    {
	if(signal_is > 0.)
	{
	    if(trace[i] > max_val)
	    {
		max_val = trace[i];
		max_pos = i;
	    }
	}
	else
	{
	    if(trace[i] < max_val)
	    {
		max_val = trace[i];
		max_pos = i;
	    }
	}
    }
    signalHeight = double(max_val - Baseline);
    Max_pos = max_pos;
    //calculate the trigger
    for (UShort_t i = max_pos; i >0; i--) 
    {
	temp =  static_cast<double>(trace[i] - Baseline);
	if(temp <= 0.3*signalHeight)
	{
	    Trigger = i;
	    break;
	}
    }
    //calculate risetime
    UShort_t interval =0;
    temp = signalHeight;
    UShort_t i = max_pos;
    if(signal_is > 0.)
    {
	while(temp > (3.*Noise) && i > 0)
	{
	    temp = static_cast<double>(trace[i] - Baseline);
	    i--;
	    interval++;
	}
    }
    else
    {
	while(temp < - (3.*Noise) && i > 0)
	{
	    temp = static_cast<double>(trace[i] - Baseline);
	    i--;
	    interval++;
	}
    }  

    RiseTime = interval * sampling_period;
//cout<< "RiseTime: "<<RiseTime<<"  height "<<signalHeight<< "  baseline "<<Baseline<<"  Noise "<<Noise<<"  Trigger "<<Trigger <<endl;

}

//------------------get the signal amplitude using the trapezoidal filter-------------------
Double_t trapezoidal_filter_algorithm( UShort_t k , UShort_t m)
{
    Double_t max_val =0.;
    UShort_t max_pos = 0;
    UShort_t l = k+m;
    Double_t signalAmplitude = 0.;
    filt_Amplitude=0;
    for(UShort_t n = 0; n <TRACE_SIZE; n++)
    {
	if(n < k)
	{
	    array_u[n] =(Double_t) trace[n] - Baseline;
	    array_v[n] = (Double_t)trace[n] - Baseline;
	}

	else
	{
	    array_u[n]= (Double_t)(trace[n]- trace[n -k]);
	}

	if(n >= l+k)
	{
	    array_v[n] = (Double_t)(trace[n-l] - trace[n-l-k]);
	}

	array_d[n] = array_u[n] - array_v[n];

	Rectangular[n] = Rectangular[n-1] + array_d[n] - (exp(- sampling_period /RC_constant) *array_d[n-1]);

	Trapezoidal[n] = Trapezoidal[n-1] + Rectangular[n];

	signalAmplitude = Trapezoidal[n]/k;

	//get max position here
	if(signal_is > 0.)
	{
	    if(Trapezoidal[n] > max_val)
	    {
		max_val = Trapezoidal[n];
		max_pos = n;
	    }
	}
	else
	{
	    if(Trapezoidal[n] < max_val)
	    {
		max_val = Trapezoidal[n];
		max_pos = n;
	    }
	}
    }
    //--
    Double_t maxR =0.; Double_t maxL = 0.;Double_t rR =0.; Double_t rL =0.;
    UShort_t j2 = max_pos + 1;
    UShort_t j1 = max_pos -1;
    // take the average from Trigger+risetime --> k+m > risetime
    if(l >= RiseTime/sampling_period)
    {
	j1 = Trigger + RiseTime/sampling_period;
	j2 = Trigger + l;
	for(UShort_t i = j1;i <j2;i++)
	{
	    maxR += Trapezoidal[j2];
	}
	max_val = maxR /(Double_t)(j2-j1);
    }
    else
    {
	if(signal_is > 0.)
	{
	    while(Trapezoidal[j2] > 0.999 * max_val)
	    {
		maxR += Trapezoidal[j2];
		j2++;
		rR++;
	    }
	    while(Trapezoidal[j1] > 0.999 * max_val)
	    {
		maxL += Trapezoidal[j1];
		j1--;
		rL++;
	    }
	}
	else
	{
	    while(Trapezoidal[j2] < 0.999 * max_val)
	    {
		maxR += Trapezoidal[j2];
		j2++;
		rR++;
	    }
	    while(Trapezoidal[j1] < 0.9999 * max_val)
	    {
		maxL += Trapezoidal[j1];
		j1--;
		rL++;
	    }
	}
	//compute average
	max_val = max_val + maxL + maxR;
	max_val = max_val /(rR+rL+1.);
    }
    //-------------
    signalAmplitude = max_val /(Double_t)(k);
   // cout<<"trap amplitude "<<signalAmplitude<<endl;
    return std::abs(signalAmplitude);
}
//-------------------main function------------------------
void calibrate(const char* infilename)
{
    //initialization
   array_u = new Double_t[TRACE_SIZE];
   array_v = new Double_t[TRACE_SIZE];
   array_d = new Double_t[TRACE_SIZE];
   Rectangular = new Double_t[TRACE_SIZE];
   Trapezoidal = new Double_t[TRACE_SIZE];
   k = new UShort_t*[NBOARDS];
   m = new UShort_t*[NBOARDS];
   for(int i = 0; i < NBOARDS; i++)
   {
	k[i] = new UShort_t[NCHANNELS];
	m[i] = new UShort_t[NCHANNELS];
    }
   set_DSSD_gain(1.); 
   for(int i = 0; i < NBOARDS; i++)
   {
        for(int j = 0; j < NCHANNELS; j++)
	{
	    k[i][j] = 200;
	    m[i][j] = 50;
	}
    }
    fBoardList[0]= 180;
    fBoardList[1]= 181;
    fBoardList[2]= 169;
    fBoardList[3]= 165;
    fBoardList[4]= 174;
    fBoardList[5]= 171;
    fBoardList[6]= 175;
    fBoardList[7]= 173;
    fBoardList[8]= 172;
    fBoardList[9]= 177;
    fBoardList[10]= 170;
    fBoardList[11]= 179;
    fBoardList[12]= 178;
    fBoardList[13]= 176;
    fBoardList[14]= 164;
    fBoardList[15]= 192;

    for (UShort_t b=0 ; b< NBOARDS; b++)
    {
	getboardIndex[ fBoardList[b] ] = b;
    }
    
   //---------get run and sub run number----------
   std::string rName(infilename);
   std::size_t pos = rName.find_first_of("_");
   std::string r0 =  rName;
   r0.erase(0, pos+1);
   pos = r0.length();
   r0.erase(4, pos); 
   std::string r1 = rName;
   pos = rName.find_last_of("_");
   r1.erase(0, pos+2); 
   pos = r1.find_first_of("-");
   r1.erase(pos, r1.length());
   if(r1.empty()) r1 = "0";
   char ofilename[200];
   sprintf(ofilename,"Spectra_%s_r%s-Numexo2.root", r0.data(), r1.data());
   TFile* oFile = new TFile(ofilename,"recreate");
   TTree* trapTree = new TTree("trapData", "trapData");
   trapTree->Branch("board", &board,"board/s");
   trapTree->Branch("boardIdx", &boardIdx,"boardIdx/s");
   trapTree->Branch("channel", &channel,"channel/s");
   trapTree->Branch("filt_Amplitude", &filt_Amplitude,"filt_Amplitude/D");
   TRandom3* rand = new TRandom3(0);
   //Fit functions
   TF1 *fLinear = new TF1("fLinear","pol1",0,10000);
   TF1 *Cball2    = new TF1("Cball2", fit_function,0,10000,10);
   //crystalball->SetParNames("Constant", "Mean", "Sigma", "Alpha", "N");
   //  TF1 *G2    = new TF1("G2", fit_function, 0,10000,10);
   TF1 *G0    = new TF1("G0","gaus",0,10000);
   G0->SetLineColor(6);
   TF1 *G1    = new TF1("G1","gaus",0,10000);
   G1->SetLineColor(2);
   TF1 *G2    = new TF1("G2","gaus",0,10000);
   G2->SetLineColor(4);
   // graph for calibration
   TGraph* gr_cal = new TGraph();
   //3 alpha source 5156.6----241Am:  5485.8----244Cm: 5804.8
   Double_t Energy[2]= {5156.6, 5804.8};
   TH2F* hCalibStrip= new TH2F("hCalibStrip","hCalib_tot; E; strips",1500,0,6000, NSTRIPS, 0, NSTRIPS);
   TH1F* htot = new TH1F("htot","hCalib_tot; E;",1500,0,6000);
   TGraphErrors* gr_fwhm = new TGraphErrors();
   TGraphErrors* gr_fwhm2 = new TGraphErrors();
   Double_t fwhm_arr[NBOARDS];
   Double_t err_fwhm_arr[NBOARDS];

   const Int_t nbins = 1000;
   Double_t xmin     = 0;
   Double_t xmax     = 4000.;
   TH1F *** hRaw = new TH1F**[NBOARDS];
   TH1F *** hCalib = new TH1F**[NBOARDS];
   Double_t **gain = new Double_t*[NBOARDS];
   Double_t **offset = new Double_t*[NBOARDS];
   for(UShort_t i = 0; i < NBOARDS;i++)
   {
       board = fBoardList[i];
       hRaw[i] = new TH1F*[NCHANNELS];
       hCalib[i] = new TH1F*[NCHANNELS];
       gain[i] = new Double_t[NCHANNELS];
       offset[i] = new Double_t[NCHANNELS];
       for(UShort_t j = 0; j < NCHANNELS;j++)
       {
	   hRaw[i][j]= new TH1F(Form("hRaw_b%d_c%d", board, j),Form("hRaw_boardId%d_channel%d", board,j),nbins,xmin,xmax);
           hCalib[i][j]= new TH1F(Form("hCalib_b%d_c%d", board,j),Form("hCalib_boardId%d_channel%d", board,j),1500,0,6000);
           gain[i][j] = 0.;
           offset[i][j] = 0.;
      }
    }

    TSpectrum *spectrum = new TSpectrum(3);
    Double_t fPositionX[3];
    Double_t fPositionY[3];
    TCanvas* canvas = new TCanvas;
    TCanvas* canvas2 = new TCanvas;

   TFile* iFile = new TFile(infilename, "READ");
   if(!iFile->IsOpen())
   {
       oFile->cd();
       oFile->Delete("T;*");
       oFile->Close();
       delete gr_cal;
       delete spectrum;
       delete canvas;
       delete canvas2;
       delete G0; delete G1; delete G2; delete fLinear;
       for(UShort_t i = 0; i < NBOARDS;i++)
       {
	   delete [] hRaw[i];
           delete [] hCalib[i];
           delete [] gain[i];
           delete [] offset[i];
           delete [] k[i];
           delete [] m[i];
        }
       delete [] hRaw;
       delete [] hCalib;
       delete [] gain;
       delete [] offset;
       delete [] k;
       delete [] m;
       delete [] array_u;
       delete [] array_v;
       delete [] array_d;
       delete [] Rectangular;
       delete [] Trapezoidal;
       delete iFile;
       delete oFile;
       std::cerr << "ERROR: could not open input file\n";
       std::terminate();
      }
      
   
   TTree* tree = (TTree*)iFile->Get("rawDataTree");
   tree->SetBranchAddress("Time", &timestamp);
   tree->SetBranchAddress("EventNo",  &eventnumber);
   tree->SetBranchAddress("Trace",  trace);
   tree->SetBranchAddress("Gain",  &Gain);
   tree->SetBranchAddress("BoardID",  &board);
   tree->SetBranchAddress("ChannelID",  &channel); 
   Long64_t nEntries = tree->GetEntries();
   //
   cout<<"Reading file.............."<<endl;
   cout<<"number of entries in the file: "<<nEntries<<endl;
   for(Long64_t entry = 0; entry < nEntries; entry++)
   {
      printProgress (entry, nEntries);
      tree->GetEntry(entry);
      boardIdx = getboardIndex[board];
      GetSignalInfo();
      //get trapezoidal amplitude
      filt_Amplitude = trapezoidal_filter_algorithm(k[boardIdx][channel], m[boardIdx][channel]);
      hRaw[boardIdx][channel]->Fill(filt_Amplitude);
      trapTree->Fill();
    }
    cout<<"Peak search in each channel begins......"<<endl;
    //-----------------------peak search and getting calibration fit parameters--------------
    //Calibrate here
    for (UShort_t bIdx = 0; bIdx < NBOARDS; bIdx++)
    {
	for(UShort_t chID = 0; chID < NCHANNELS; chID++) 
	{
	    cout<<"board: "<<fBoardList[bIdx]<<" channel: "<<chID<<endl;
	    canvas->cd();
	    hRaw[bIdx][chID]->Draw("");
	    
	    PressEnterToContinue();
            
	    hRaw[bIdx][chID]->GetXaxis()->SetRangeUser(800.,4500.);
	    if( hRaw[bIdx][chID]->GetEntries() < 100) continue;
            
            //Find the peaks
            Int_t nfound = spectrum->Search(hRaw[bIdx][chID], 2, "", 0.05); //hist, sigma, option, threshold
            Float_t *xpeaks = spectrum->GetPositionX();
	    if(nfound ==3)
	    {
		 Int_t idx[nfound];
            TMath::Sort(nfound,xpeaks,idx,false);
            for (Int_t i = 0; i < nfound; i++) 
	    {
		fPositionX[i] = xpeaks[idx[i]];
		Int_t bin = hRaw[bIdx][chID]->GetXaxis()->FindBin(fPositionX[i]);
                fPositionY[i] = hRaw[bIdx][chID]->GetBinContent(bin);
		cout<<"peak i: "<<i<<" x  "<<fPositionX[i]<<"  y "<<fPositionY[i]<<endl; 
	    }
 
            //fit 1 peak first
            G0->SetRange(fPositionX[0]-30,fPositionX[0]+30);
            G0->SetParameters(fPositionY[0],fPositionX[0], 15.);
            hRaw[bIdx][chID]->Fit(G0,"QMR");
            Double_t sigma = G0->GetParameter(2);
            //Set Range for the fit functions
            G1->SetRange(fPositionX[0]-1*sigma,fPositionX[0]+2*sigma);
            G2->SetRange(fPositionX[2]-1*sigma,fPositionX[2]+2*sigma);
            //set parameters
	    //G1->SetParameters(fPositionY[0],fPositionX[0],2.5,1,3, fPositionY[1],fPositionX[1],2.5,1,3);
	    //G2->SetParameters(fPositionY[4],fPositionX[4],2.5,1,3, fPositionY[5],fPositionX[5],2.5,1,3);
            G1->SetParameters(fPositionY[0],fPositionX[0],sigma);
            G2->SetParameters(fPositionY[2],fPositionX[2],sigma);
            G1->SetParLimits(2, 1., 30.);
            G2->SetParLimits(2, 1., 30.);
            hRaw[bIdx][chID]->Fit(G1,"MR+");
            hRaw[bIdx][chID]->Fit(G2,"MR+");
	    canvas->Update();
            // Calibration
	    fPositionX[0] = G1->GetParameter(1);
            fPositionX[1] = G2->GetParameter(1);
            for (Int_t pt(0); pt<2; pt++) 
	    {
		gr_cal->SetPoint(pt,fPositionX[pt], Energy[pt]);
             }
	    canvas2->cd();
            gr_cal->Draw();
            gr_cal->Fit(fLinear,"M","same");
	   canvas2->Update();
            //Get Parameters
            gain[bIdx][chID] =  fLinear->GetParameter(1);
            offset[bIdx][chID] = fLinear->GetParameter(0);
	    
	    
	    }
           
        }
    }
    //-----------------------calibrate-----------------
    cout<<"Calibration started..............."<<endl;
    Double_t calibData = 0.;
    
    for(Long64_t i = 0; i < trapTree->GetEntries();i++){
      trapTree->GetEntry(i);
      calibData = gain[boardIdx][channel]*filt_Amplitude  + offset[boardIdx][channel];
      hCalib[boardIdx][channel]->Fill(calibData);
      stripnumber = get_DSSD_strip_number(&board, &channel);
      hCalibStrip->Fill(calibData, stripnumber);
      htot->Fill(calibData);
      
    }
    cout<<"Fit 5.8 MeV peak----------------"<<endl;
    vector<resolution_strip>minRes; int bin1, bin2; double height, height1, sigma, temp;
    //optimize k and m
    for(UShort_t bIdx = 0; bIdx < NBOARDS; bIdx++)
    {
	fwhm_arr[bIdx] =0.; err_fwhm_arr[bIdx] =0.;
    }
    int counter =0;
    for(UShort_t bIdx = 0; bIdx < NBOARDS; bIdx++){
      for(UShort_t chID = 0; chID < NCHANNELS; chID++){
        if( hCalib[bIdx][chID]->GetEntries() < 100) continue;
        hCalib[bIdx][chID]->GetXaxis()->SetRangeUser(5700.,6000.);
        canvas->cd();
        hCalib[bIdx][chID]->Draw();
        height= hCalib[bIdx][chID]->GetMaximum();
        G0->SetRange(5800-100.,5800+100.);
        G0->SetParameters(height, 5805,10.);
        hCalib[bIdx][chID]->Fit(G0,"QMR");
        sigma = G0->GetParameter(2);
          
        G1->SetRange(5805-3*sigma,5805+3*sigma);
        G1->SetParameters(height, 5805,sigma);
         
        G1->SetParameters(height, 5805,sigma);
        hCalib[bIdx][chID]->Fit(G1,"MR+");
        //max in the range
        bin1 =  hCalib[bIdx][chID]->GetXaxis()->FindBin(5750);
        bin2 =  hCalib[bIdx][chID]->GetXaxis()->FindBin(5780);
        height1 = hCalib[bIdx][chID]->GetBinContent(bin1);
        for(int i = bin1; i <= bin2;i++){
          temp = hCalib[bIdx][chID]->GetBinContent(i);
          if(height1 < temp)
            height1 = temp; 
        }

        Cball2->SetRange(5740,5850);
        Cball2->SetParameters(height1, 5762, sigma, 10, 3, height, 5805,sigma, 10, 3);
        hCalib[bIdx][chID]->Fit(Cball2,"MR+");
          
        UShort_t board = fBoardList[bIdx];
        Double_t FWHM = Cball2->GetParameter(7)*2.35;
	Double_t errFWHM = Cball2->GetParError(7)*2.35;
        UShort_t k_val = k[bIdx][chID];
        UShort_t m_val = m[bIdx][chID];
      
        fwhm_arr[bIdx] += FWHM;
	stripnumber = get_DSSD_strip_number(&fBoardList[bIdx], &chID);
	err_fwhm_arr[bIdx] += errFWHM*errFWHM;
	gr_fwhm2->SetPoint(counter, stripnumber, FWHM);
        gr_fwhm2->SetPointError(counter, 0, errFWHM);
        resolution_strip r(board, chID,  k_val, m_val , FWHM);
        minRes.push_back(r);
	counter++;
      }
      // take average
      fwhm_arr[bIdx] = fwhm_arr[bIdx]/16.;
      err_fwhm_arr[bIdx] = sqrt(err_fwhm_arr[bIdx]);
      err_fwhm_arr[bIdx] = err_fwhm_arr[bIdx]/16.;
    }
  //get the strip with min Resolution
    std::sort(minRes.begin(), minRes.end(), compareFWHM);

    cout<<"minimum FWHM: "<<minRes[0].FWHM <<"  board: "<<minRes[0].board<<"  channel: "<<minRes[0].channel<<"  k: "<<minRes[0].k<<"  m: "<<minRes[0].m<<endl;
    
    minRes.clear();

// fill the fwhm graph
   for(UShort_t bIdx = 0; bIdx < NBOARDS; bIdx++)
   {
       gr_fwhm->SetPoint(bIdx, fBoardList[bIdx], fwhm_arr[bIdx]);
       gr_fwhm->SetPointError(bIdx, 0, err_fwhm_arr[bIdx]);
       
    }
   gr_fwhm->SetNameTitle("gr_fwhmB","FWHM at 5.8 MeV vs Board Id");
   gr_fwhm->SetMarkerColor(4);
   gr_fwhm->SetMarkerStyle(21);
   
   gr_fwhm2->SetNameTitle("gr_fwhmS","FWHM at 5.8 MeV vs Strip number");
   gr_fwhm2->SetMarkerColor(2);
   gr_fwhm2->SetMarkerStyle(21);
   
    ///gettotal res

    bin1 =  htot->GetXaxis()->FindBin(5750);
    bin2 =  htot->GetXaxis()->FindBin(5780);
    height1 = htot->GetBinContent(bin1);
    for(int i = bin1; i <= bin2;i++){
      temp = htot->GetBinContent(i);
      if(height1 < temp)
        height1 = temp; 
    }
    htot->GetXaxis()->SetRangeUser(5700.,6000.);
    canvas->cd();
    htot->Draw();
    height= htot->GetMaximum();
          
    Cball2->SetRange(5740,5850);
    Cball2->SetParameters(height1, 5762, sigma, 10, 3, height, 5805,sigma, 10, 3);
    htot->Fit(Cball2,"MR");
    canvas->Update();
    sigma = Cball2->GetParameter(7);
    double FWHM = sigma*2.35;
    cout<<"FWHM total: "<<FWHM<<endl;

    //from the function
    Double_t maxf = Cball2->GetMaximum(5805-sigma, 5805+sigma);

    maxf = maxf/2.;

    Double_t x1 = Cball2->GetX(maxf, 5805-2*sigma, 5805);
    Double_t x2 = Cball2->GetX(maxf, 5805, 5805+2*sigma); 

    cout<<"new FWHM "<<x2-x1<<endl;

 //--------------reached end---------------
   //close input file
   iFile->cd();
   iFile->Close();
   //save spectra and close output file
   oFile->cd();
   oFile->Write();
   gr_fwhm->Write();
   gr_fwhm2->Write();
   oFile->Close();
   
//-----------------------------end-------------
//clear memory
    cout<<"Clearing memory..................";
    delete [] array_u;
    delete [] array_v;
    delete [] array_d;
    delete [] Rectangular;
    delete [] Trapezoidal;
    delete rand;
    
    delete gr_cal;
    delete spectrum;
    delete canvas;
    delete canvas2;
    delete G0; delete G1; delete G2; delete fLinear; delete Cball2; 
    for(UShort_t i = 0; i < NBOARDS;i++){
      delete [] k[i];
      delete [] m[i];
      delete [] hRaw[i];
      delete [] hCalib[i];
      delete [] gain[i];
      delete [] offset[i];    
    }
    delete [] k;
    delete [] m;
    delete [] hRaw;
    delete [] hCalib;
    delete [] gain;
    delete [] offset; 
    
    delete iFile;
    delete oFile;
    
}
