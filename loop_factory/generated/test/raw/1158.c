int main1(){
  int r, te, r0, g3, va;

  r=(1%28)+9;
  te=0;
  r0=0;
  g3=(1%28)+10;
  va=-4;

  while (g3>r0) {
      g3 -= r0;
      va += r;
      r0 = r0 + 1;
      va = va + te;
  }

}
