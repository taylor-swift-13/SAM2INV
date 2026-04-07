int main1(){
  int khn, y, ch, m6;

  khn=(1%38)+11;
  y=0;
  ch=0;
  m6=-2;

  while (y < khn) {
      y++;
      ch = ch + m6;
      m6 = m6 + ch;
  }

}
