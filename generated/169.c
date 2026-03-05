int main169(int r){
  int ir5, f16, g, fb7, o3;

  ir5=r+21;
  f16=1;
  g=-8;
  fb7=4;
  o3=0;

  while (f16<=ir5-1) {
      o3 = o3*o3+g;
      g = g%4;
      if ((f16%9)==0) {
          fb7 = g*g;
      }
      fb7 = fb7*fb7+g;
      if (o3+6<ir5) {
          g = g%2;
      }
      f16 = f16*3;
  }

}
