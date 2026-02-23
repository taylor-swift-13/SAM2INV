int main1(int k,int m){
  int b, g, o, v;

  b=67;
  g=b;
  o=b;
  v=k;

  while (o!=0&&v!=0) {
      if (o>v) {
          o = o-v;
      }
      else {
          v = v-o;
      }
      o = o*2;
  }

}
