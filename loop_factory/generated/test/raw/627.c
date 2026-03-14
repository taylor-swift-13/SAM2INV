int main1(int n){
  int k1, j5s, tx, zao;

  k1=16;
  j5s=0;
  tx=1;
  zao=1;

  for (; j5s<k1; j5s++) {
      if (!(tx<9)) {
          zao = -1;
      }
      if (tx<=1) {
          zao = 1;
      }
      tx += zao;
  }

}
