int main1(){
  int i8, mi, x, wa;

  i8=63;
  mi=0;
  x=-2;
  wa=0;

  while (1) {
      if (!(mi<i8)) {
          break;
      }
      if (wa<i8) {
          x = mi;
      }
      wa = wa + 1;
      mi++;
  }

}
