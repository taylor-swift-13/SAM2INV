int main186(int y,int q,int j){
  int l5vw, f9, xhdl, o, o8e;

  l5vw=(j%25)+20;
  f9=0;
  xhdl=26;
  o=1;
  o8e=0;

  while (xhdl>0&&o<=l5vw) {
      if (xhdl>o) {
          xhdl = xhdl - o;
      }
      else {
          xhdl = 0;
      }
      y = y+xhdl-xhdl;
      o8e++;
      f9 = f9 + 1;
      o = o + 1;
  }

}
