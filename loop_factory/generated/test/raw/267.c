int main1(){
  int v99, kv, iq, crag;

  v99=1+13;
  kv=0;
  iq=1;
  crag=1;

  while (kv<v99) {
      if (iq>=5) {
          crag = -1;
      }
      if (!(iq>1)) {
          crag = 1;
      }
      kv = kv + 1;
      iq = iq + crag;
  }

}
