int main1(){
  int btb, f, nq5, xx, nm5v, d8, t9;

  btb=58;
  f=0;
  nq5=(1%40)+2;
  xx=0;
  nm5v=btb;
  d8=f;
  t9=btb;

  while (nq5!=xx) {
      xx = nq5;
      nm5v = nm5v+(xx%2);
      nq5 = (nq5+btb/nq5)/2;
      nm5v = nm5v*2;
      t9 += nq5;
      d8 = d8+(nq5%2);
  }

}
