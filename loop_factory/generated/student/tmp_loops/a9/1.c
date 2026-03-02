int main1(int a,int k){
  int o, h, v;

  o=29;
  h=o;
  v=o;

  while (h>1) {
      v = v+2;
      if ((h%4)==0) {
          v = v+1;
      }
      else {
          v = v+v;
      }
      v = v+h;
  }

}
