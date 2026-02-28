int main1(int k,int m,int p){
  int z, u, j, v;

  z=m;
  u=0;
  j=0;
  v=0;

  while (j<z) {
      if (j<z/2) {
          v = v+3;
      }
      else {
          v = v-3;
      }
      j = j+1;
      v = v-1;
      v = k;
      if (j+1<z) {
          j = j+1;
      }
      v = v+j;
  }

}
