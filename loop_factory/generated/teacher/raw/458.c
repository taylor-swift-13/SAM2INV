int main1(int m,int q){
  int j, k, x;

  j=(m%6)+19;
  k=1;
  x=q;

  while (1) {
      x = x+3;
      x = x+6;
      if (k+7<=k+j) {
          x = x+x;
      }
  }

}
