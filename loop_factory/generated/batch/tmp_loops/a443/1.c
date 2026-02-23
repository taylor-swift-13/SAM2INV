int main1(int b,int k){
  int w, v, u;

  w=b+25;
  v=0;
  u=v;

  while (v<=w-2) {
      u = u+3;
      if (u+7<w) {
          u = u+u;
      }
      else {
          u = u+v;
      }
  }

}
