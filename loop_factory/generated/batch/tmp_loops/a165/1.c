int main1(int k,int n){
  int l, e, y, f;

  l=(k%33)+11;
  e=0;
  y=n;
  f=0;

  while (e<l) {
      if (e<l/2) {
          y = y+f;
      }
      else {
          y = y+1;
      }
      y = y+1;
      f = f+3;
  }

}
