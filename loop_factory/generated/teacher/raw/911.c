int main1(int k,int m){
  int i, r, x, d;

  i=(k%6)+11;
  r=i;
  x=3;
  d=r;

  while (r>=4) {
      d = d+1;
      x = d*d;
      x = x+d;
  }

}
