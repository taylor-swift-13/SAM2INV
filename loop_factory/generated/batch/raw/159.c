int main1(int n){
  int r, j, v;

  r=n;
  j=4;
  v=n;

  while (j<r) {
      if ((j%9)==0) {
          v = v-v;
      }
      else {
          v = v+1;
      }
      j = j+1;
  }

}
