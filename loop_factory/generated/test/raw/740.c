int main1(int a,int v){
  int p, fj, x, eft;

  p=0;
  fj=0;
  x=(a%28)+10;
  eft=p;

  while (x>fj) {
      x -= fj;
      eft = eft+(x%5);
      fj++;
  }

}
