int main1(int m,int n){
  int h, e, c;

  h=n-5;
  e=2;
  c=m;

  while (1) {
      c = c+3;
      if (c+5<h) {
          c = c+c;
      }
      c = c+c;
  }

}
