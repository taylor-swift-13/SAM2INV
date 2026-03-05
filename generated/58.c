int main58(int p,int q){
  int x, pbl, vu, t, ye7;

  x=(q%35)+10;
  pbl=p;
  vu=8;
  t=1;
  ye7=3;

  while (pbl<=x) {
      vu = vu*pbl;
      if (pbl<x) {
          t = t*pbl;
      }
      pbl = pbl + 1;
      ye7 = ye7*4;
      p = p/4;
      q += pbl;
  }

}
