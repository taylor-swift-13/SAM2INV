int main1(){
  int e3, sxv, gk, vw, tr;

  e3=(1%7)+6;
  sxv=1;
  gk=(1%40)+2;
  vw=0;
  tr=sxv;

  while (gk!=vw) {
      vw = gk;
      gk = (gk+e3/gk)/2;
      tr += gk;
      tr = tr*4+5;
  }

}
