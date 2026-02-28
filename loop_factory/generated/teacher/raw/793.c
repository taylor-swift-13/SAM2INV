int main1(int a,int q){
  int h, b, c, r;

  h=(q%7)+16;
  b=h;
  c=b;
  r=b;

  while (b>=2) {
      r = c;
      c = c+2;
      c = c+1;
      r = r+c;
  }

}
