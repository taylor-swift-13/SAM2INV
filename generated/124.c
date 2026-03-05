int main124(int t,int j){
  int ti7, kt1, li, pe, l, gu;

  ti7=j+21;
  kt1=ti7;
  li=40;
  pe=1;
  l=0;
  gu=ti7;

  while (li>0&&pe<=ti7) {
      if (li>pe) {
          li = li - pe;
      }
      else {
          li = 0;
      }
      kt1 += 1;
      l = l + 1;
      pe = pe + 1;
      gu = gu+li-l;
  }

}
