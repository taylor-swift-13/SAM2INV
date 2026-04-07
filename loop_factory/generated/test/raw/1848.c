int main1(){
  int jx, ba, i1c, t6, a, ak, kx;

  jx=(1%11)+16;
  ba=0;
  i1c=ba;
  t6=0;
  a=6;
  ak=ba;
  kx=-4;

  while (1) {
      if (a==jx+1) {
          i1c = i1c + 3;
          t6 = t6 + 3;
      }
      else {
          i1c += 2;
          t6 += 2;
      }
      if (a==jx) {
          i1c++;
          a++;
      }
      ak += t6;
      ak = ak + 3;
      kx = kx + 3;
      ba = ba + 1;
      if (!(!(ba>=jx))) {
          break;
      }
  }

}
