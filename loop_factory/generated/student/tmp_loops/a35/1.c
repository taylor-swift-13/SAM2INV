int main1(int m,int p){
  int u, i, c, k;

  u=p-5;
  i=3;
  c=-8849;
  k=m;

  while (c+8<0) {
      c = c+k+1;
      k = k+3;
      c = c*c+c;
      c = c%4;
  }

}
