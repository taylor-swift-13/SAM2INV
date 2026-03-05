int main47(int t,int p){
  int x8, tyu, o3;

  x8=(p%8)+11;
  tyu=x8;
  o3=0;

  while (tyu<=x8-1) {
      o3 += 2;
      tyu = tyu + 1;
      t += o3;
      t = t+p+p;
  }

}
