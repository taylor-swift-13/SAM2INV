int main1(int u,int j){
  int eex, id, cts, v2;

  eex=u+10;
  id=eex;
  cts=-3;
  v2=u;

  while (cts<eex) {
      v2 = eex-cts;
      j = j + id;
      cts += 2;
  }

  while (v2<eex) {
      cts = (eex)+(-(v2));
      u = u + id;
      v2 = v2 + 1;
  }

}
