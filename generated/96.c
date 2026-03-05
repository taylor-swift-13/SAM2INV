int main96(int r){
  int l1, q, hb, am8y, o, t;

  l1=r*4;
  q=l1;
  hb=20;
  am8y=l1;
  o=q;
  t=0;

  while (1) {
      if (!(q<=l1-1)) {
          break;
      }
      q += 1;
      hb += 2;
      t = t+(hb%8);
      am8y += hb;
      r = r+(hb%5);
      o = o + 3;
  }

}
