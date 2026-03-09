int main1(int r,int a){
  int nr, dfr, e1yb, fp;

  nr=55;
  dfr=1;
  e1yb=0;
  fp=3;

  while (1) {
      if (!(dfr<nr)) {
          break;
      }
      dfr = 2*dfr;
      e1yb = e1yb + 1;
      r += dfr;
      fp = fp*3+(dfr%6)+1;
  }

}
