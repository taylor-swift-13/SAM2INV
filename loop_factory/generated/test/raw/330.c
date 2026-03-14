int main1(int s){
  int a2kq, nc, gs, ine, j5, sqed;

  a2kq=s+10;
  nc=a2kq;
  gs=0;
  ine=0;
  j5=nc;
  sqed=0;

  while (1) {
      if (!(ine<a2kq)) {
          break;
      }
      gs = gs + s;
      ine++;
      j5 += gs;
      j5 = j5*j5+j5;
  }

  while (a2kq<=gs-1) {
      a2kq++;
      j5 = j5 + s;
      sqed = sqed*2;
      s = s+gs-nc;
  }

}
