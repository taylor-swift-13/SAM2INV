int main1(int a,int k,int p,int q){
  int m, i, x, w;

  m=(k%29)+10;
  i=0;
  x=1;
  w=4;

  while (1) {
      if (i>=m) {
          break;
      }
      x = x+2;
      i = i+1;
      x = x+1;
      w = w-1;
      w = w+1;
  }

}
