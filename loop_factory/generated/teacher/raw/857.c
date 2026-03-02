int main1(int k,int q){
  int x, o, b, r;

  x=36;
  o=0;
  b=6;
  r=1;

  while (1) {
      if (o>=x) {
          break;
      }
      b = b+2;
      o = o+1;
      b = b+r+r;
  }

}
