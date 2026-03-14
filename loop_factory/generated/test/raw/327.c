int main1(int j){
  int t6z, v2e, x, a, yiw, tf7c;

  t6z=65;
  v2e=0;
  x=0;
  a=0;
  yiw=t6z;
  tf7c=4;

  while (1) {
      if (!(a<t6z)) {
          break;
      }
      a++;
      x += j;
      tf7c += 2;
      yiw = yiw + a;
  }

  while (a<x) {
      v2e += j;
      a++;
      tf7c = tf7c + v2e;
      tf7c = tf7c + yiw;
  }

}
