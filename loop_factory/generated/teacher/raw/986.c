int main1(int k,int n){
  int y, t, a;

  y=k-2;
  t=1;
  a=8;

  while (t<=y/3) {
      a = a%6;
      a = a*a;
      t = t*3;
  }

}
