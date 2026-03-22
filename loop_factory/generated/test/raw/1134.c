int main1(){
  int k4m, c2, s, xg, b, j, d29g;

  k4m=76;
  c2=-2;
  s=0;
  xg=0;
  b=0;
  j=4;
  d29g=0;

  for (; c2<k4m; c2 += 1) {
      if (c2%3==0) {
          if (s>0) {
              s -= 1;
              b += 1;
          }
      }
      else {
          if (s<j) {
              s++;
              xg++;
          }
      }
      d29g++;
  }

}
