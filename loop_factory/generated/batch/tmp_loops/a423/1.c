int main1(int k,int n){
  int h, t, x, d;

  h=k;
  t=2;
  x=k;
  d=k;

  while (t<=h-3) {
      if (x+3<=h) {
          x = x+3;
      }
      else {
          x = h;
      }
      x = x*2;
  }

}
