int main1(int a){
  int res, j0, h, d;

  res=a-3;
  j0=res;
  h=res;
  d=1;

  while (j0 < res) {
      h += d;
      j0++;
      d = d * a;
  }

}
