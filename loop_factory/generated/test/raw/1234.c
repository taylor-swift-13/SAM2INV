int main1(){
  int hdkj, rnb, o0, dm, a03, q, hj0;

  hdkj=(1%24)+8;
  rnb=1;
  o0=0;
  dm=4;
  a03=13;
  q=rnb;
  hj0=0;

  while (1) {
      if (q>hdkj) {
          break;
      }
      o0 = o0 + dm;
      dm += a03;
      a03 = (2)+(a03);
      q += 1;
      hj0 = hj0+(o0%4);
  }

}
