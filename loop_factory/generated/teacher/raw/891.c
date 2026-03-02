int main1(int a,int k){
  int l, r, m;

  l=k;
  r=0;
  m=l;

  while (1) {
      m = m+2;
      if ((r%5)==0) {
          m = m*m;
      }
      else {
          m = m*m+m;
      }
  }

}
