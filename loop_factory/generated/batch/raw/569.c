int main1(int b,int p){
  int h, q, v, k;

  h=(p%21)+14;
  q=0;
  v=q;
  k=-5;

  while (1) {
      v = v*v+v;
      v = v%3;
      if (q+5<=v+h) {
          v = k*k;
      }
      q = q+1;
  }

}
