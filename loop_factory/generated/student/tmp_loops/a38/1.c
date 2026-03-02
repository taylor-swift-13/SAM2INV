int main1(int b,int q){
  int y, i, v;

  y=(q%25)+6;
  i=3;
  v=1;

  while (i<=y-1) {
      v = v+2;
      if ((i%9)==0) {
          v = v-v;
      }
      else {
          v = v+v;
      }
      v = v+i;
  }

}
