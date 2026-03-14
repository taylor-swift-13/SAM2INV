int main1(int i,int n){
  int b9lr, nz, nx3;

  b9lr=78;
  nz=0;
  nx3=0;

  while (1) {
      if (!(nx3<b9lr)) {
          break;
      }
      nz = (nz+1)%3;
      nx3 += 1;
      n += 2;
      i = (i+nz)%8;
  }

}
