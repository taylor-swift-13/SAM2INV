int main1(int a,int b){
  int p, r, v, m;

  p=(b%28)+16;
  r=p;
  v=-4;
  m=b;

  while (r-1>=0) {
      v = v+1;
      m = m-1;
      v = v+m;
  }

}
