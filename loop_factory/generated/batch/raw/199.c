int main1(int p,int q){
  int i, b, v;

  i=53;
  b=0;
  v=-1;

  while (b<=i-1) {
      v = v*v+v;
      if (b+4<=v+i) {
          v = v*2;
      }
      b = b+1;
  }

  while (v+1<=i) {
      v = v+1;
  }

  while (v-1>=0) {
      v = v-1;
  }

}
