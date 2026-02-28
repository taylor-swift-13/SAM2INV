int main1(int a,int m){
  int w, t, v;

  w=a+4;
  t=w;
  v=-6;

  while (t-3>=0) {
      v = v+3;
      v = v-v;
      if ((t%3)==0) {
          v = v+v;
      }
  }

}
