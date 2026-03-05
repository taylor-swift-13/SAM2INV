int main128(int j,int r){
  int ti4v, k87, cqr;

  ti4v=r*4;
  k87=0;
  cqr=0;

  while (1) {
      if (!(cqr<=ti4v-1)) {
          break;
      }
      k87 = (k87+1)%7;
      cqr += 1;
      r += 2;
      j = (j+cqr)%7;
      j++;
  }

}
