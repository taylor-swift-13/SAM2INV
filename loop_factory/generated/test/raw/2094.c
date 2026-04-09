int main1(int k){
  int bld, tx, a;

  bld=k;
  tx=0;
  a=0;

  while (tx<bld) {
      if (!(!(tx>=bld/2))) {
          a += 2;
      }
      tx += 1;
      k += bld;
  }

}
