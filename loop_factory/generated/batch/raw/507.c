int main1(int b,int p){
  int h, q, v, k;

  h=(p%21)+14;
  q=0;
  v=0;
  k=-5;

  while (1) {
      k = h-v;
      v = v+1;
      v = v+k+k;
      if (q+5<=v+h) {
          k = k+h;
      }
      else {
          v = v+q;
      }
  }

}
