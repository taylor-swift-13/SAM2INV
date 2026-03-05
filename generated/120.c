int main120(int r){
  int y, m, tx, e2, b6, gnu;

  y=89;
  m=2;
  tx=r;
  e2=-6;
  b6=m;
  gnu=(r%6)+2;

  while (1) {
      if (!(b6<=y-1)) {
          break;
      }
      b6 += 1;
      e2 = e2*gnu;
      tx = tx*gnu+r;
      gnu += b6;
      gnu = gnu*gnu+gnu;
  }

}
