int main1(int t,int u){
  int uh, bjc, j, tp56, f86;

  uh=(u%38)+4;
  bjc=uh;
  j=0;
  tp56=0;
  f86=u;

  while (j<=uh-1) {
      tp56 = j+2;
      j += 4;
      f86 = f86 + tp56;
  }

  while (tp56<bjc) {
      f86 += t;
      tp56 += 1;
      t = t + tp56;
  }

}
