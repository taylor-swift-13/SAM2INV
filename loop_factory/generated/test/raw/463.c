int main1(){
  int l, m, ws5, blh, f;

  l=1;
  m=l;
  ws5=0;
  blh=0;
  f=3;

  while (blh<=l-1) {
      f = f + m;
      ws5 += 1;
      blh++;
  }

  while (blh<=f-1) {
      blh++;
      l = l + 1;
      if (l+5<f) {
          l += l;
      }
  }

}
