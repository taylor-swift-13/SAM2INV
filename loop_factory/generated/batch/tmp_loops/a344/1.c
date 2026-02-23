int main1(int k,int m){
  int x, i, w;

  x=15;
  i=x;
  w=i;

  while (i>=2) {
      w = w%8;
      if (i*i<=x+3) {
          w = w+i;
      }
      i = i-2;
  }

}
