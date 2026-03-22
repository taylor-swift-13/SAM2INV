int main1(){
  int db, m7o, w, gg, o, ta;

  db=1*2;
  m7o=db+1;
  w=(1%40)+2;
  gg=0;
  o=2;
  ta=m7o;

  while (1) {
      if (!(w!=gg)) {
          break;
      }
      gg = w;
      w = (w+db/w)/2;
      o = o + w;
      ta = ta+(w%2);
      o = o + m7o;
      ta = ta*ta;
  }

}
