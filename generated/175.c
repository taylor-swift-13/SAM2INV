int main175(int t,int g,int c){
  int myo, bn, fm, gt3, db;

  myo=3;
  bn=-11055;
  fm=-8;
  gt3=myo;
  db=t;

  while (bn<=-4) {
      bn = bn+fm-3;
      fm++;
      c += 2;
      db = db+(bn%2);
      g += 2;
      gt3 = gt3+(bn%4);
  }

}
