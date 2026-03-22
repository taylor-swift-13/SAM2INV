int main1(int g,int i){
  int io, j, qd, kzjy, o2ua, p, m3x, wp, v79;

  io=(i%6)+6;
  j=0;
  qd=g;
  kzjy=-1;
  o2ua=5;
  p=i;
  m3x=g;
  wp=g;
  v79=io;

  while (j < io) {
      qd = j % 3;
      p = (p + g) % 13;
      o2ua = (o2ua * 2 + i) % 11;
      kzjy = (kzjy + qd) % 7;
      m3x = (m3x + j) % 17;
      v79 = (v79 + m3x) % 23;
      j++;
      wp = (wp + o2ua) % 19;
      if (i+6<io) {
          i = i + 1;
      }
      if ((j%9)==0) {
          i += 6;
      }
      i = i + i;
      g += m3x;
  }

}
