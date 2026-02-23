int main1(int n,int p){
  int s, j, m, b;

  s=(p%14)+7;
  j=s+3;
  m=-2;
  b=4;

  while (j>1) {
      m = m*2+5;
      b = b*m+5;
      m = m*3+3;
  }

}
