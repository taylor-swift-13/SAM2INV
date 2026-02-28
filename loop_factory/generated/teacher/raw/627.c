int main1(int a,int n){
  int w, f, r;

  w=n+11;
  f=0;
  r=-6;

  while (f<=w-1) {
      if (r+5<w) {
          r = r-r;
      }
      else {
          r = r+r;
      }
      f = f+1;
  }

}
