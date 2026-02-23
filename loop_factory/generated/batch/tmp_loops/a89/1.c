int main1(int a,int b){
  int y, i, v, m;

  y=b-7;
  i=0;
  v=a;
  m=b;

  while (i<y) {
      v = v*3+5;
      m = m*v+5;
      v = v+m;
  }

}
