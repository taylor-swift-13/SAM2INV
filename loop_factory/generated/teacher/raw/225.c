int main1(int m,int n){
  int w, t, d;

  w=79;
  t=0;
  d=w;

  while (t<=w-2) {
      d = d-d;
      if ((t%2)==0) {
          d = d+1;
      }
      t = t+2;
  }

}
