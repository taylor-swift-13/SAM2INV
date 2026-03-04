int main1(){
  int ts, w, xch;

  ts=(1%6)+12;
  w=2;
  xch=ts;

  while (w<ts) {
      xch += 1;
      w += 1;
      xch = xch + xch;
  }

}
