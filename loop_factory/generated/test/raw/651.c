int main1(int o){
  int m6, nl, h, m5x;

  m6=o-8;
  nl=m6;
  h=0;
  m5x=-1;

  while (h<m6) {
      m5x = m6-h;
      o += nl;
      h += 1;
  }

  while (1) {
      if (!(nl<m6)) {
          break;
      }
      nl += 1;
      o = o + m6;
      h = m6-nl;
  }

}
