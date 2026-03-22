int main1(){
  int oi, v7l, pc7, s, kg1, lgx;

  oi=68;
  v7l=3;
  pc7=0;
  s=0;
  kg1=0;
  lgx=6;

  while (v7l<oi) {
      s = v7l%5;
      if (!(!(v7l>=lgx))) {
          kg1 = (v7l-lgx)%5;
          pc7 = pc7+s-kg1;
      }
      else {
          pc7 = pc7 + s;
      }
      v7l += 1;
      lgx = lgx + kg1;
  }

}
